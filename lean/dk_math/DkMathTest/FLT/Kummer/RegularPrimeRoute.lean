/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.RegularPrimeRoute

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Kummer Branch Test — axioms 監視

Kummer branch の各 theorem の axiom 依存を監視する。
sorry を使っている theorem はそれとして識別し、
no-sorry の theorem が意図せず sorry に汚染されていないことを確認する。

ここは新規に作られた定理の早期チェックのための専用ファイルである。
ビルド時間が長くなったので、既に確認済みの定理は、

- `RegularPrimeRouteNoSorry.lean`
- `RegularPrimeRouteSorry.lean`

へ、移してある。上記、Test Lean は、適宜確認してステータスの変化がないかを監視する。

ここに置くべき `#print axioms` 監視は、`RegularPrimeRoute.lean` の定理の新規実装定理の確認限定である。
-/

-- no-sorry
-- None

-- `sorry`
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelExactErrorDescent_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute
