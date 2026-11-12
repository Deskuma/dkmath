/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- 一般核
import DkMath.Lib.Cosmic.Completion

-- Pascal の素数行
import DkMath.NumberTheory.BinomialPrime

-- 原始支持と周期世界
import DkMath.NumberTheory.Primitive.SquareBody
import DkMath.NumberTheory.Primitive.SquarePrimeExpansion
import DkMath.NumberTheory.Primitive.PeriodicPrimeWorld
import DkMath.NumberTheory.Primitive.PrimeWorldResidues
import DkMath.NumberTheory.Primitive.PrimeWorldRefinement

-- primorial 世界との橋
import DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge
import DkMath.NumberTheory.PrimorialUniverse.ThirtySquareWorld
import DkMath.NumberTheory.PrimorialUniverse.UnitCoordinateRefinement

-- Legendre consumer
import DkMath.NumberTheory.Legendre.PrimeWorldPacketBridge
import DkMath.NumberTheory.Legendre.PrimorialWheelBridge
import DkMath.NumberTheory.Legendre.GnomonPascalCell
import DkMath.NumberTheory.Legendre.PacketCoprimality
import DkMath.NumberTheory.Legendre.GnomonBridge

#print "file: DkMath.NumberTheory.Completion"

/-!
# 完成算術から素数世界・平方殻への数論入口

一般的な GN・完成不足・付値は `DkMath.Lib.Cosmic.Completion` が所有者への入口となる。
このファイルは、その数学を使う Primitive・PrimorialUniverse・Legendre の既存consumerを公開する。
定理本体を移動・複製せず、各所有者の名前空間と仮定を保持する。

## 教科書としてたどる順序

1. Pascalの素数行で、内側二項係数の可除性を読む。
2. `Primitive.squareBody` の平方完成と素数支持を読み、周期modulusと生存剰余へ進む。
3. primorial世界では有限の素数基底と、その積の単位座標を区別する。
   30の例は具体例であり、有限基底に含まれない全ての数が素数になるわけではない。
4. Legendre側では生存剰余・packet・wheel・平方殻・Pascal cellの対応を読む。
   支持を除外した点の素数判定と、そのような点の存在は別の命題である。

たとえば `legendreConjecture_iff_projectedWheelEscape_from_two` は
Legendre予想をwheel脱出の存在へ翻訳する同値である。
この入口をimportしても、その存在条件や予想そのものが新しく証明されるわけではない。
同様にunit座標を細分したときは同じ実数点を保持し、座標の素数性は保持するとは限らない。

この応用層はLibの依存先にしない。一般核だけを使うconsumerにはLib側の入口がある。
-/
