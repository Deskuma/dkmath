/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- ============================================================================
-- Lean の `inductive` の使い方の例：カレー料理の型を定義する
-- ============================================================================

/-! 【 inductive の説明 】

inductive は、Lean におけるデータ型を定義するためのキーワードです。
inductive を使用すると、複数のコンストラクタを持つデータ型を定義できます。

例えば、自然数型 Nat は以下のように定義されます。

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

この定義により、Nat 型の値は zero または succ コンストラクタを使用して構築されます。

inductive は、リストやオプション型など、さまざまなデータ構造を定義するために広く使用されます。

-/

-- 例えば、食べ物のカレーを型として定義すると、以下のようになります。

/-- カレー料理 Curry Dish 型 -/
inductive CurryDish : Type where
  | vegCurry : CurryDish  -- 野菜カレー
  | chickenCurry : CurryDish  -- チキンカレー
  | beefCurry : CurryDish  -- ビーフカレー

-- このように、CurryDish 型の値は vegCurry、chickenCurry、beefCurry のいずれかで構築されます。

-- CurryDish 型の使用例

-- 私のお気に入りのカレー料理を定義します。
def myFavoriteCurry : CurryDish := CurryDish.chickenCurry  -- チキンカレー
#eval myFavoriteCurry  -- 出力: chickenCurry

-- カレー料理がベジタリアンかどうかを判定する関数
def isVegetarian (dish : CurryDish) : Bool :=
  match dish with
  | CurryDish.vegCurry => true
  | _ => false
#eval isVegetarian myFavoriteCurry  -- 出力: false

-- カレー料理がビーフカレーかどうかを判定する関数
def isBeefCurry (dish : CurryDish) : Bool :=
  match dish with
  | CurryDish.beefCurry => true
  | _ => false
#eval isBeefCurry myFavoriteCurry  -- 出力: false

-- カレー料理がチキンカレーかどうかを判定する関数
def isChickenCurry (dish : CurryDish) : Bool :=
  match dish with
  | CurryDish.chickenCurry => true
  | _ => false
#eval isChickenCurry myFavoriteCurry  -- 出力: true

-- カレー料理の名前を文字列として返す関数
def CurryDishToString (dish : CurryDish) : String :=
  match dish with
  | CurryDish.vegCurry => "Vegetable Curry"
  | CurryDish.chickenCurry => "Chicken Curry"
  | CurryDish.beefCurry => "Beef Curry"

#eval CurryDishToString myFavoriteCurry  -- 出力: "Chicken Curry"

-- 以上のように、inductive を使用してカレー料理の型を定義し、その型に基づく関数を作成しました。
