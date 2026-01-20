/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- ----------------------------------------------------------------------------
namespace DkMath.Samples.ClassInstance

/-!
  # クラスインスタンスの例

  Lean の型クラスとインスタンスの使い方の例を示します。
-/

-- ----------------------------------------------------------------------------
namespace GreetExample01

/--
  「挨拶できる」型クラス
-/
class Greet (α : Type) where
  greet : α → String

/--
  Nat は挨拶できる、という instance を登録
-/
instance : Greet Nat where
  greet n := "Nat: " ++ toString n

/--
  String も挨拶できる、という instance
-/
instance : Greet String where
  greet s := "String: " ++ s

/--
  ここがポイント：
  [Greet α] を引数に取ると、
  「α の Greet instance を自動で探して」くれる。
-/
def sayHello (α : Type) [Greet α] (x : α) : String :=
  Greet.greet x

#eval sayHello Nat 7
#eval sayHello String "Lean"

end GreetExample01

-- ----------------------------------------------------------------------------
namespace GreetExample02

class Greet (α : Type) where
  greet : α → String

instance : Greet Nat where
  greet n := "Nat: " ++ toString n

-- 辞書（instance）を明示的に受け取る版
def sayHello' (α : Type) (inst : Greet α) (x : α) : String :=
  inst.greet x

-- ふつうの型クラス版（inst が暗黙で渡される）
def sayHello (α : Type) [Greet α] (x : α) : String :=
  Greet.greet x

#eval sayHello Nat 3
#eval sayHello' Nat (by infer_instance) 3

end GreetExample02

-- ----------------------------------------------------------------------------
namespace GreetExample03

class Greet (α : Type) where
  greet : α → String

instance : Greet Nat where
  greet n := toString n

-- α に Greet があるなら、List α にも Greet を作る
instance (α : Type) [Greet α] : Greet (List α) where
  greet xs :=
    "[" ++ String.intercalate ", " (xs.map Greet.greet) ++ "]"

def sayHello (α : Type) [Greet α] (x : α) : String :=
  Greet.greet x

#eval sayHello (List Nat) [1,2,3]

end GreetExample03

-- ----------------------------------------------------------------------------
namespace GreetExample04

/-!
超重要：どうやって「どの instance が使われてるか」確認する？

#synth が便利（型クラス推論の結果を見せてくれる）
-/

class Greet (α : Type) where
  greet : α → String

instance : Greet Nat where
  greet n := toString n

#synth Greet Nat

end GreetExample04

-- ----------------------------------------------------------------------------
end DkMath.Samples.ClassInstance

-- ---------------------------------------------------------------------------/

/-
次の展開として：

- 同じ型に instance を2つ作って競合させてみる（エラー例）
- attribute [instance] や local instance の話
- mathlib の Semiring とかで「実際にどう使われてるか」

-/

-- cid: 696e99ac-f5cc-8322-a486-441f8fcaa6ec
