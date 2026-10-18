# NOTE-002 セクション4・5の実施 — 固定契約と交換可能な供給

2026-10-18。対象は NOTE-002 の改善点と研究契約。新たな指数別 FLT や GN による共役の代替証明は追加しない。
既存の係数定理・Packet・Conditions と FLT11/13 の公開型を維持して、供給側と消費側を分離した。

## 4.1 GN と古典的 Kummer の境界

| 処理 | 実際の担当 | 受け渡す数学的対象 |
|---|---|---|
| GN 因子抽出 | 既存 `GN_kummer_structure_of_first_case` | 同じ線形因子 `a+ζb=εγ^p`、単元と根を保持 |
| 因子から位相式 | 既定の `classical_factor_packet_provider` | `CaseIConjugation.Packet` |
| 既定供給の証明本体 | `UnitConjugation`、`CaseIConjugationPacket` | CM 共役・単元比・p 乗の合同 |
| Case I の終端 | `GNCaseIContract` | 非合同な向き付けと `Packet.false_of_not_modEq` |
| 中立な係数障害 | `SparsePhaseObstruction` | 空位相と整数係数の可除性 |
| Case II の終端 | 既存整数入口と `RegularDescent.no_state` | 原始性・非零性・正深度を保つ State |

ここでいう GN 因子抽出は、GN／円分イデアルの橋と、イデアル冪分解・類群消去の
既存算術を合成する API である。GN 恒等式だけから元の p 乗表示を得ているわけではない。
`GN_p=t^p` という整数ノルムの結論だけから矛盾を導くものでもない。
現在の Case I の既定供給は古典的な共役単元を使う。この出所は docstring と依存監査に明示した。
Case II は引き続き証明済みの底・実際の後続 State 構成・正深度帰納法を使う。

## 4.2 交換可能な供給と互換アダプタ

新しい `CaseIConjugationContract.lean` に Packet の宣言を移した。
namespace・引数・フィールド・構成子の型は維持する。
従来の `CaseIConjugationPacket` の import からも同じ名前で利用できる。
固定型のファイルは最小限の Mathlib 依存だけを持つ `module` とし、
古典的供給の既存 `module` 形式も維持した。係数剛性による消費定理は GN 側に置く。

二つの明示的な命題を追加した。

- `CaseIConjugation.FactorPacketProvider ζ`：**同じ** `u*α^p=a+ζb` の表示から Packet を供給する。
- `CaseIConjugation.SolutionPacketProvider ζ`：原始的 Case I 方程式から Packet を供給する。

これらは公理や型クラスではない。呼出側が証明項を渡す契約である。
因子契約では単元 u と根 α の同一性を保ち、方程式契約では原始性と `p∤abc` を保つ。

`GNCaseIContract` は、任意の因子供給と既存 GN 抽出を合成する。
`RegularPrimeContract` は、任意の方程式供給と `RegularDescent.Conditions` から、
整数・自然数の一般終端を証明する。
両ファイルは具体的な `UnitConjugation`・Kummer 単元 criterion の実供給・11/13 PID を import しない。

従来の `GNCaseIObstruction` と `RegularPrimeFLT` は、証明済みの古典的供給と算術条件を渡す既定アダプタとした。
既存の公開定理に provider 引数は追加していない。
`ElevenThirteenFLT` の定理本体は変更せず、docstring に非零条件だけを補記した。

将来の供給を使う形は次の通り。

```lean
-- source は新しい GN 証明などによって実際に証明する必要がある。
-- C の5フィールドも、それぞれ実際に証明して渡す。
fermatLastTheoremWith_int_of_phase_contracts hζ hp5 hodd source C
fermatLastTheoremFor_of_phase_contracts hζ hp5 hodd source C
```

これにより、新しい証明を別モジュールに追加でき、固定した終端や既存11/13特殊化を書き換える必要がない。
今回、新たな GN 供給の証明を完成したという主張はしない。

## 4.3 整数版の非零条件

`FermatLastTheoremWith ℤ p` は

```lean
∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a^p + b^p ≠ c^p
```

という述語である。符号と共通因子の制限を除いても、`a,b,c≠0` は残る。
p>0 なら `0^p+1^p=1^p` が成立するため、零を含めた排除は偽である。
一般整数入口・11/13整数入口の docstring、README、NOTE-001 実装報告にこの条件を明記した。
回帰検査にも、この自明解による反例を加えた。

## 5. 固定する三契約

| 契約 | 固定する型と意味 | 将来変更できる部分 |
|---|---|---|
| `phase_sum_dvd_iff` | 素数 p、原始根、任意の整数 m に対する双方向同値。`CharZero` 以上の NumberField 仮定を追加しない | GN の位相係数保存則は別定理として追加 |
| `CaseIConjugation.Packet` | `k₁,k₂ : Fin p`、`k₂ ≡ k₁-1 mod p`、整数 p の像による4項式の可除性 | Packet の構成証明。原始根・p≥5 は消費時に別途要求 |
| `RegularDescent.Conditions` | 下記5フィールドの型 | 類群・単元 criterion・分岐の供給証明 |

Conditions のフィールドは次のままである。

```lean
odd          : Odd p
three_le     : 3 ≤ p
ramification : (p : R) ∣ P.lambda ^ (p - 1)
class_group  : classGroupPTorsionFreeAt R p
unit_power   : KummerUnitPowerCriterion R p
```

底・降下ステップ・反例排除を仮定するフィールドは追加しない。
State 0 は排除せず、Case II の降下は引き続き正深度に限定する。

## 検証と証跡

`PhaseContractBoundary` は具体的な古典的供給を import しない環境で、三契約の型と
任意の供給証明からの整数／自然数終端を検査する。
環境中に共役・単元 criterion・11/13 PID の具体的供給が現れた場合は失敗する。
`PhasePacketModuleCompatibility` は既存供給を `module` 形式から import する互換性を検査する。
既存 `PhaseRigidityFLT` は従来の一般入口と11/13の型互換性を引き続き検査する。

依存監査は従来36宣言に追加13宣言を加えた49宣言を扱う。
11/13の証明グラフは、新しい抽象終端に加えて、実際の古典的 Packet 供給・
算術 Conditions・PID・整数入口・共通降下が含まれることを要求する。
旧 Case I 互換入口のグラフも独立に検査する。
単なる内部互換名の出現要求を新しい消費側と供給側の出現要求へ置き換え、
必要な数学的 provider の検査は維持した。

最終コマンドと結果は [evidence/validation-note002.txt](evidence/validation-note002.txt) に保存した。

最終統合ビルドは11,472 jobsで成功した。49宣言の公理監査、三契約の型・import境界、
既存 module import、ルート公開入口と `DkMathTest.lean` の直接検査も通過した。
変更・追加した本体と検査に新規警告はなく、監査した証明グラフの公理は
`propext`・`Classical.choice`・`Quot.sound` のみだった。
