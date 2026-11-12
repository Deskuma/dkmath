/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.Completion
import DkMath.NumberTheory.Completion
import DkMath.CosmicFormula.CosmicFormulaBinom
import DkMath.Gnomon.Algebra
import DkMath.Gnomon.CosmicBridge
import DkMath.Lib.Cosmic.GTailSeven
import DkMath.Lib.Cosmic.GTailSevenArithmetic

#print "file: DkMath.Completion"

/-!
# GN・完成算術の研究用統合入口

`DkMath.Lib.Cosmic.Completion` の一般核と、`DkMath.NumberTheory.Completion` の
素数世界・平方殻consumerをまとめ、既存のCosmicFormula・Gnomon・七次の教材へ接続する。
このファイルはimportだけの入口であり、定義・定理・証明本体を追加しない。

平方殻は `Gnomon.squareGnomonBand_eq_mul_GTail_two_one` により
GTailの二次特殊化と同じ量として読める。Big・Body・Gapの旧語彙は
`CosmicFormulaBinom` に、一般の完成不足 R_n・D_n はLibの所有者に残る。
七次の二項展開・係数内容・付値は固定次数の例であり、一般の素数次数の結論へ強めない。

完成の恒等式、素数支持、素数冪の深さ、原始三項の構成を段階的に読むための研究入口である。
これらの対応だけでFLTの降下やLegendre平方区間の素数存在を結論しない。
軽い一般核だけが必要なら `DkMath.Lib.Cosmic.Completion` を利用する。
-/
