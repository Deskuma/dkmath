/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.BinomTail

#print "file: DkMath.Algebra.BinomTail"

/-!
# BinomTailの互換入口

[DkMath.Lib] GN-LIB-003a: 一般尾項・正性の5補題の所有者を
`DkMath.Lib.Algebra.BinomTail` へ移管した。
従来の `DkMath.Algebra.BinomTail` namespace、全修飾名、型を保持する。
新しい一般consumerはLib側を直接importできる。
このファイルは同名宣言の再定義を行わず、旧importの到達性を保存する。
-/
