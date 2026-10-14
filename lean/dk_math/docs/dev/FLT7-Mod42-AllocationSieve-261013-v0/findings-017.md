# findings-017 — source-indexed obstruction and source frontier

2026-10-14。Part A: Outcome A。constructive bridge subtask: Outcome B（局所化した未解決存在）。

actual core の等式 `internalDepthFourSeventhCore p = c*ℓ^n` を明示的仮定として保持し、gate016 の排除と source reconstruction/full-sieve equivalence を接続した。再構成を仮定したときの core inequality と、同じ carrier の finite charts 不存在も薄い系として証明した。いずれも arbitrary arithmetic M を actual packet core と暗黙に同定していない。

既存索引で source reconstruction equivalences 9件を確認し、今回の source obstruction 名は0件。実ソースの定義・必要仮定・import 経路を確認した。production 新規モジュールは gate016 module だけを import し、source equivalences は既存 transitive imports で解決した。

source-coupling-map-005 と現在の real-pair load / loaded recovery を照合した。source は実際の K、A,B、M、補根 N と積/coprimality ledger、realPair gcd loads と stripped associated powers を供給する。loaded recovery は row-two cell powers をさらに要求する。chart 構成に最初に不足するのは指定 carrier の自然数 additive endpoints の存在である。normal-form theorem は別途 CounterexamplePack を要求し、その pack を作らない。

[ source-bridge-frontier-017.md ](source-bridge-frontier-017.md) に同じ packet の provenance map、最初の missing formula の数学表現と Lean-proposed type、loaded 経路に先行する cell-power 不足、phase/valuation の制約を記録した。未証明目標は文書だけに置き、新しい仮定や axiom として production に追加していない。

DkMathTest で conditional hcore の法11・法13/c=1,3,13 の例、reconstructed-core constraint、source ledger facts、loaded split の source-only 存在、root-ne-innerRoot の適用を検証した。signature probes と direct-use failure probes は必要な supplied pack / cell assumptions を確認したが、数学的な独立性や全証明の不可能性は示さない。

calibration exit 0、focused build exit 0（9091 jobs）、最終 test exit 0。公開3定理の公理は propext、Classical.choice、Quot.sound のみ、sorryAx なし。新規 prime/modulus/numeric core 探索は行っていない。

新しい constructive bridge は導いていない。hcore は source data から導かれた factorization ではない。packet の不存在、全 packet の reconstruction 否定、source/chart bridge、FLT7 は結論していない。gate017 で終了する。
