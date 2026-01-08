import Mathlib

namespace DkMath
namespace Polyomino

abbrev Cell := ℤ × ℤ  -- セルは整数格子点のペアで表現
abbrev PolyominoType := Finset Cell  -- 有限集合としてのポリオミノ

-- 面積（セル数）
def area (P : PolyominoType) : ℕ := P.card  -- 有限集合の要素数

end Polyomino
end DkMath
