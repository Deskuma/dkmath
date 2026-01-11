/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- Curry 型を定義します。
inductive Curry (α β γ : Type) : Type where
  | mk : (α → β → γ) → Curry α β γ

/- 解説:
  Curry 型は、関数型プログラミングにおけるカリー化を表現します。
  mk コンストラクタは、2つの引数を取る関数をカリー化された形式で保持します。

  カリー化とは？
  カリー化とは、複数の引数を取る関数を、1つの引数を取る関数の連鎖に変換する技法です。
  例えば、関数 f : α → β → γ は、f : α → (β → γ) として表現されます。
  これにより、部分適用が可能になり、関数の柔軟な利用が促進されます。

  例: Curry 型の使用例
  let addCurry : Curry Nat Nat Nat := Curry.mk (fun x y => x + y)
  let addFive : Nat → Nat := match addCurry with
    | Curry.mk f => f 5
  let result : Nat := addFive 10  -- result は 15 になります

  まとめ:
  Curry 型は、関数のカリー化を表現し、部分適用を可能にするための型です。
  これにより、関数型プログラミングにおける柔軟な関数利用が促進されます。
-/

-- Curry 型の使用例
def addCurry : Curry Nat Nat Nat := Curry.mk (fun x y => x + y)

def addFive : Nat → Nat := match addCurry with
  | Curry.mk f => f 5

def result : Nat := addFive 10  -- result は 15 になります

#eval result  -- 出力: 15
