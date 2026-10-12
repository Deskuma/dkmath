# findings-004 — global rejection and unbounded survivors

## Initial source audit

- instruction-004 / review-003 を確認。開始時の研究ブランチに変更なし。実装・検証・報告のみ、Git mutation なし。
- gate-003 の二定義、exact-to-cheap implication と reconstruction consumer の実際の型を確認。
- mod-42 bridge は divisor guard を保持。sixth-power condition の modulus-one theorem を再利用する。
- `Nat.pos_of_mem_divisors` と `Nat.pow_le_pow_left` で全 divisor に対する 554 の排除を試す。
- family は base integer inequality と monotonicity、modular arithmetic で全自然数 k に証明する。bounded samples だけでは済ませない。
- conditional reconstruction consumer は既存 implication の対偶だけであり、packet の存在を構成しない。

## Plan

新規の小さな audit module で全-divisor exclusion、631+42*k family、modulus-one sixth-power condition、明示的な unbounded survivor theorem を証明する。554 / 589 の対比と一般適用を DkMathTest に残す。既存の exact receivers と stable proof files は変更しない。

## Initial calibration

Index build: exit 0、1,805 files / 29,265 declarations。`search --name mod42Cheap --limit 20` は既存 gate-003 の二含意だけ。新しい排除 / family は未実装。

初回 calibration は exit 1: `/1` を除く `change` は定義的等値でなく失敗した。命題の反例ではない。既存 `Nat.div_one` を明示的に書き換えて修正する。その他の証明 target にエラーなし。

## Production and test checkpoint

- 修正 calibration は exit 0。production と再利用する gate-003 test dependency の focused build も exit 0（9091 jobs）。
- 最初の final test は exit 1: injectivity example の lambda 適用が omega に未展開のまま渡された。等式の型を `change` で明示して beta reduction を行い、omega に渡す。family / unbounded / exclusion 本体にエラーなし。

## Final outcome

- Outcome A。最終 test exit 0、warning/error なし。
- 全 divisor の 554 排除、conditional reconstruction exclusion、全 k の family と任意 B を超える survivors が証明された。
- test で family injectivity と既存 589 survivor の対比も成功。
- 六 exports のうち sixth-power family は propext のみ、その他は標準三公理。sorryAx なし。
- 現在の cheap conditions (+r=1 sixth-power) 単独では全候補の不在を導けない。source-coupled ledger / chart / endpoint constraints の調査を次に提案し、今回は未実装。
- 既存 source は変更なし。Git mutation なし、logs は ignored。compact evidence の provenance は Codex-reported。
