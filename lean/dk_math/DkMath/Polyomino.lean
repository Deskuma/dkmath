import Mathlib

namespace DkMath
namespace Polyomino

abbrev Cell := ℤ × ℤ  -- セルは整数格子点のペアで表現
abbrev Shape := Finset Cell  -- 有限集合としてのポリオミノ

-- 面積（セル数）
def area (P : Shape) : ℕ := P.card  -- 有限集合の要素数

end Polyomino
end DkMath
